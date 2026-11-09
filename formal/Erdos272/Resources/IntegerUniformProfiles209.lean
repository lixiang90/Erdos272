module

public import Erdos272.Resources.IntegerUniformRows209
public import Erdos272.Arithmetic.IntegerLowPrices209
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.GetD

@[expose] public section

namespace JSP233.IntegerUniformProfiles209
open StarCompletion APGeometry SourceBridge208 SevenFamily208 CrossBandCredit208 CrossBandCleanup208
open IntegerHighPrices209 IntegerLowPrices209 IntegerUniformRows209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def W (w : Fin 11) : Window := windows.getD w.val ⟨0,0,[]⟩
def count (w : Fin 11) : ℕ := [32,16,16,16,8,8,8,8,8,8,8].getD w.val 0
def heights (w : Fin 11) : Array ℚ := #[#[0,58713,114195,167973,212903,250165,313150,373942,424454,482271,521114,560948,589206,626252,657087,688825,721317,754412,787961,821816,864357,881717,899412,917406,935662,954142,972809,991625,1010553,1029556,1048596,1067816,1077558],#[0,118731,219036,332789,439971,525029,607331,676177,741306,800365,851898,903960,967760,1005532,1043892,1082546,1111965],#[0,123531,231093,347564,457127,544122,635036,705326,780313,832106,884775,946894,1002614,1050755,1089981,1129531,1159518],#[0,133140,244198,376780,490308,587278,681626,754387,831863,894371,948894,1013162,1080572,1120452,1171173,1212108,1243182],#[0,276340,549846,759198,926657,1078744,1198388,1293707,1380347],#[0,319255,635438,885552,1075526,1260310,1389152,1514868,1608452],#[0,404645,809010,1117331,1362856,1593745,1762980,1917327,2035740],#[0,576047,1144184,1586943,1929895,2259862,2504529,2719023,2891433],#[0,971435,1948071,2693204,3272065,3826407,4238213,4596745,4902630],#[0,2144608,4281014,5928299,7202625,8423767,9339512,10137765,10803694],#[0,7043223,14032771,19426819,23641551,27628500,30592081,33158677,35403802]][w.val]!
def phi (w : Fin 11) (k : ℕ) : ℚ := (heights w)[min k (count w)]!
def psi (w : Fin 11) (k : ℕ) : ℝ := phi w k
def row (w : Fin 11) (k : ℕ) : Row := (W w).rows.getD k ⟨0,0,[]⟩

def Facts (w : Fin 11) : Prop :=
    count w=(W w).rows.length ∧ (W w).M=M w ∧ (W w).high=Upper w ∧
    (heights w).size=count w+1 ∧ phi w 0=0 ∧ 0<phi w (count w) ∧
    ∀i : Fin (count w),(row w i.val).height=(heights w)[i.val+1]! ∧
      (heights w)[i.val]!≤(heights w)[i.val+1]!
instance (w : Fin 11) : Decidable (Facts w) := by unfold Facts;infer_instance

theorem facts (w : Fin 11) : Facts w := by fin_cases w <;> decide +kernel
theorem reciprocal (w : Fin 11) : 1195/(42*(M w : ℝ)*psi w (count w))=G w := by
  fin_cases w <;> norm_num [M,G,psi,phi,heights,count]

theorem W_mem (w : Fin 11) : W w∈windows := by
  have hl : windows.length=11 := by decide +kernel
  have hi : w.val<windows.length := by rw [hl];exact w.isLt
  rw [W,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem row_mem (w : Fin 11) (i : Fin (count w)) : row w i.val∈(W w).rows := by
  have hi : i.val<(W w).rows.length := by rw [←(facts w).1];exact i.isLt
  rw [row,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem psi_zero (w : Fin 11) : psi w 0=0 := by
  dsimp only [psi]
  exact_mod_cast (facts w).2.2.2.2.1
theorem psi_pos (w : Fin 11) : 0<psi w (count w) := by
  dsimp only [psi]
  exact_mod_cast (facts w).2.2.2.2.2.1
theorem psi_mono (w : Fin 11) : Monotone (psi w) := by
  have hm := UniformPotential208.capped_monotone (heights w) (count w)
    (fun i=>(facts w).2.2.2.2.2.2 i |>.2)
  intro i j hij
  dsimp only [psi,phi]
  exact_mod_cast hm hij

def actual_recipe {N : ℕ} (w : Fin 11) (i : Fin (count w)) (hN : N≤Upper w) :
    IntegerUniformSystem209.Recipe N (W w).M (row w i.val).e i.val (psi w) := by
  have hh : psi w (i.val+1)≤(row w i.val).height := by
    have hi : min (i.val+1) (count w)=i.val+1 := by omega
    have he := ((facts w).2.2.2.2.2.2 i).1
    simp only [psi,phi,hi]
    exact_mod_cast he.ge
  have hp := IntegerUniformRows209.recipe (N := N) (k := i.val) (psi := psi w)
    (W_mem w) (row_mem w i) (by rw [(facts w).2.2.1];exact hN) hh
  exact hp

theorem actual_system {N : ℕ} {A : Finset (Finset ℤ)}
    (w : Fin 11) (i : Fin (count w)) (hN : 2≤N) (hhi : N≤Upper w)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M w≤S.card) (hsparse : ∀S∈A,11*S.card≤N) :
    ∃s : System,s.N=N ∧ s.D=N/(M w-(row w i.val).e) ∧ s.M=M w ∧
      s.e=(row w i.val).e ∧ s.F=JointNear N A 1 (M w) (psi w) i.val ∧
      (∀d b,s.T d b=(band (row w i.val) b).T ∧ s.E d b=(band (row w i.val) b).E ∧
        s.U d b=(band (row w i.val) b).U ∧ s.B d b=CleanupEval208.block (band (row w i.val) b) d) ∧ Valid s := by
  have hf := IntegerUniformRows209.facts (W_mem w) (row_mem w i)
  have hM : 2≤(W w).M := by have hh:=hf.1;omega
  have hs : ∀S∈A,(W w).M≤S.card := by simpa only [(facts w).2.1] using hsize
  have hh := IntegerUniformSystem209.actual_system (actual_recipe w i hhi) hM hf.2.1 hf.2.2.1 hN
    hlegal hbad hs hsparse
  simpa only [(facts w).2.1,actual_recipe,IntegerUniformRows209.recipe] using hh

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)} (w : Fin 11)
    (bill : ℕ→ℝ)
    (hcount : ∀i<count w,((JointNear N A 1 (M w) (psi w) i).card : ℝ)≤bill i)
    (hpaid : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*bill i)/(psi w (count w))≤
      U w*(N : ℝ)^2+Eta w*N) : IntegerShared209.NearObligation N A (M w) (G w) (U w) (Eta w) := by
  refine ⟨psi w,count w,psi_mono w,psi_zero w,psi_pos w,reciprocal w,?_⟩
  have hh : (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*
      ((JointNear N A 1 (M w) (psi w) i).card : ℝ))≤
      ∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*bill i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hcount i (Finset.mem_range.mp hi))
      (sub_nonneg.mpr (psi_mono w (Nat.le_succ i)))
  exact (div_le_div_of_nonneg_right hh (psi_pos w).le).trans hpaid

#print axioms reciprocal
#print axioms actual_recipe
#print axioms actual_system
#print axioms actual_obligation
end
end JSP233.IntegerUniformProfiles209
