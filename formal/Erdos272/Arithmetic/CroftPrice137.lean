import Erdos272.Resources.FarCut134
import Erdos272.Arithmetic.ConvexPrice134
import Erdos272.Counting.FiniteNear136

namespace JSP233.CroftPrice137
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Budget : ℝ := 4437/50000
def Beta : ℝ := 21/242
def NuNumerator : ℝ := FiniteNear136.NuNumerator
def EtaNumerator : ℝ := 798
def FarCoefficient (k : ℕ) : ℝ :=
  4/(3*(FarCut134.Mass k:ℝ)*FarCut134.Cutoff k)
def Price (a b c x : ℝ) : ℝ := a*x+b+c/x
def Whole (n k : ℕ) : ℝ :=
  Price (FarCoefficient k) (NuNumerator/k) (EtaNumerator) n
def Direct (n k c : ℕ) : ℝ := Price 0 0 ((c:ℝ)*(3*(k:ℝ))) n
def RootA (n k : ℕ) : ℝ :=
  Price (FarCoefficient k) (NuNumerator/k) (6*k+EtaNumerator) n
def RootB (n k : ℕ) : ℝ :=
  Price 0 (Beta+6*k*FarCoefficient k/Beta)
    (6*NuNumerator/Beta+EtaNumerator) n
def Root (n k : ℕ) : ℝ := max (RootA n k) (RootB n k)

def ParameterBudget (n k d c : ℕ) : Prop :=
  600≤d ∧ d≤k ∧ 3*d≤c ∧ c≤3*k ∧ 3*k≤n ∧
    Direct n k c≤Budget ∧ Whole n k≤Budget ∧
    Whole n d≤Budget ∧ Root n k≤Budget

theorem parameter_window {n lo hi k d c : ℕ}
    (hl : lo≤n) (hu : n≤hi) (hpos : 0<lo)
    (hshape : 600≤d ∧ d≤k ∧ 3*d≤c ∧ c≤3*k ∧ 3*k≤lo)
    (hDirect : Direct lo k c≤Budget ∧ Direct hi k c≤Budget)
    (hWholeK : Whole lo k≤Budget ∧ Whole hi k≤Budget)
    (hWholeD : Whole lo d≤Budget ∧ Whole hi d≤Budget)
    (hRootA : RootA lo k≤Budget ∧ RootA hi k≤Budget)
    (hRootB : RootB lo k≤Budget ∧ RootB hi k≤Budget) :
    ParameterBudget n k d c := by
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

theorem parameters750 {N:ℕ} (hlo:64660617≤N) (hhi:N≤71425022) :
    ParameterBudget N 750 750 2250 := by
  apply parameter_window hlo hhi (by norm_num)
  all_goals norm_num [Direct,Whole,RootA,RootB,Price,FarCoefficient,
    FarCut134.Mass,FarCut134.Cutoff,FarJoint113.Mass,
    NuNumerator,FiniteNear136.NuNumerator,EtaNumerator,Beta,Budget]

theorem actual_parameters {N:ℕ} (hlo:64660617≤N) (hhi:N≤71425022) :
    ∃k d c:ℕ,ParameterBudget N k d c :=
  ⟨750,750,2250,parameters750 hlo hhi⟩

#print axioms parameter_window
#print axioms parameters750
#print axioms actual_parameters
end
end JSP233.CroftPrice137
