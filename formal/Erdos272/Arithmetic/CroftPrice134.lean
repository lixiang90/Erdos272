module

public import Erdos272.Resources.FarCut134
public import Erdos272.Arithmetic.ConvexPrice134

@[expose] public section

namespace JSP233.CroftPrice134
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Budget : ℝ := 4437/50000
def Beta : ℝ := 21/242
def NuNumerator : ℝ := 2303/200
def EtaNumerator (j : ℕ) : ℝ := (7/2)*(j:ℝ)^2
def FarCoefficient (k : ℕ) : ℝ :=
  2/((FarCut134.Mass k:ℝ)*FarCut134.Cutoff k)
def Price (a b c x : ℝ) : ℝ := a*x+b+c/x
def Whole (n j k : ℕ) : ℝ :=
  Price (FarCoefficient k) (NuNumerator/k) (EtaNumerator j) n
def Direct (n k c : ℕ) : ℝ := Price 0 0 ((c:ℝ)*(3*(k:ℝ))) n
def RootA (n j k : ℕ) : ℝ :=
  Price (FarCoefficient k) (NuNumerator/k) (6*k+EtaNumerator j) n
def RootB (n j k : ℕ) : ℝ :=
  Price 0 (Beta+6*k*FarCoefficient k/Beta)
    (6*NuNumerator/Beta+EtaNumerator j) n
def Root (n j k : ℕ) : ℝ := max (RootA n j k) (RootB n j k)

def ParameterBudget (n j k d c : ℕ) : Prop :=
  1≤d ∧ d≤k ∧ 3*d≤c ∧ c≤3*k ∧ 3*k≤n ∧
    Direct n k c≤Budget ∧ Whole n j k≤Budget ∧
    Whole n j d≤Budget ∧ Root n j k≤Budget

theorem parameter_window {n lo hi j k d c : ℕ}
    (hl : lo≤n) (hu : n≤hi) (hpos : 0<lo)
    (hshape : 1≤d ∧ d≤k ∧ 3*d≤c ∧ c≤3*k ∧ 3*k≤lo)
    (hDirect : Direct lo k c≤Budget ∧ Direct hi k c≤Budget)
    (hWholeK : Whole lo j k≤Budget ∧ Whole hi j k≤Budget)
    (hWholeD : Whole lo j d≤Budget ∧ Whole hi j d≤Budget)
    (hRootA : RootA lo j k≤Budget ∧ RootA hi j k≤Budget)
    (hRootB : RootB lo j k≤Budget ∧ RootB hi j k≤Budget) :
    ParameterBudget n j k d c := by
  have hlR : (lo:ℝ)≤n := by exact_mod_cast hl
  have huR : (n:ℝ)≤hi := by exact_mod_cast hu
  have hpR : (0:ℝ)<lo := by exact_mod_cast hpos
  have hgk : (0:ℝ)≤FarCoefficient k := by unfold FarCoefficient; positivity
  have hgd : (0:ℝ)≤FarCoefficient d := by unfold FarCoefficient; positivity
  refine ⟨hshape.1,hshape.2.1,hshape.2.2.1,hshape.2.2.2.1,
    hshape.2.2.2.2.trans hl,?_,?_,?_,?_⟩
  · exact ConvexPrice134.price_window (by norm_num) hpR hlR huR hDirect.1 hDirect.2
  · exact ConvexPrice134.price_window hgk hpR hlR huR hWholeK.1 hWholeK.2
  · exact ConvexPrice134.price_window hgd hpR hlR huR hWholeD.1 hWholeD.2
  · apply max_le
    · exact ConvexPrice134.price_window hgk hpR hlR huR hRootA.1 hRootA.2
    · exact ConvexPrice134.price_window (by norm_num) hpR hlR huR hRootB.1 hRootB.2

theorem parameters854 {N : ℕ} (hlo : 73967140≤N) (hhi : N≤74169584) :
    ParameterBudget N 27 854 854 2562 := by
  apply parameter_window hlo hhi (by norm_num)
  all_goals norm_num [Direct,Whole,RootA,RootB,Price,FarCoefficient,
    FarCut134.Mass,FarCut134.Cutoff,FarJoint113.Mass,
    NuNumerator,EtaNumerator,Beta,Budget]

theorem parameters855 {N : ℕ} (hlo : 74169585≤N) (hhi : N≤74320000) :
    ParameterBudget N 27 855 855 2565 := by
  apply parameter_window hlo hhi (by norm_num)
  all_goals norm_num [Direct,Whole,RootA,RootB,Price,FarCoefficient,
    FarCut134.Mass,FarCut134.Cutoff,FarJoint113.Mass,
    NuNumerator,EtaNumerator,Beta,Budget]

theorem actual_parameters {N : ℕ} (hlo : 73967140≤N) (hhi : N≤74320000) :
    ∃k d c:ℕ,ParameterBudget N 27 k d c := by
  by_cases hcut : N≤74169584
  · exact ⟨854,854,2562,parameters854 hlo hcut⟩
  · exact ⟨855,855,2565,parameters855 (by omega) hhi⟩

#print axioms parameter_window
#print axioms parameters854
#print axioms parameters855
#print axioms actual_parameters
end
end JSP233.CroftPrice134
