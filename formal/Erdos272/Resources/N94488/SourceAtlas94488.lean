module

public import Erdos272.Arithmetic.N94488.SourceQueryFloors94488
public import Erdos272.Arithmetic.N94488.SourceRunFloors94488
public import Erdos272.Counting.N94488.RunFacts94488
public import Erdos272.Resources.N109474.RunSource109474
public import Erdos272.Resources.N109474.CorrelatedSource109474
public import Erdos272.Resources.N130000.RowSources130000
public import Erdos272.Resources.N142758.RowSources142758
public import Erdos272.Resources.N150465.RowSources150465
public import Erdos272.Resources.N109474.SourceAtlas109474

@[expose] public section

namespace JSP233.SourceAtlas94488
open StarCompletion SourceBridge208 IntrinsicTriples208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Contract where
  lower : ℕ
  defect : ℕ
  target : ℕ

structure Provider where
  kind : ℕ
  index : ℕ

def ofPlan (q : CorrelatedSource158375.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩
def ofRun (q : RunSource109474.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩

def oldContract (i : ℕ) : Contract :=
  match i with
  | 0 => ofPlan (SourceQueryData142758.query 122)
  | 1 => ⟨(SourceAtlas109474.demand 11).lower,(SourceAtlas109474.demand 11).defect,(SourceAtlas109474.demand 11).target⟩
  | 2 => ofPlan (SourceQueryData130000.query 17)
  | 3 => ⟨(SourceAtlas109474.demand 142).lower,(SourceAtlas109474.demand 142).defect,(SourceAtlas109474.demand 142).target⟩
  | 4 => ofPlan (SourceQueryData142758.query 136)
  | 5 => ⟨(SourceAtlas109474.demand 151).lower,(SourceAtlas109474.demand 151).defect,(SourceAtlas109474.demand 151).target⟩
  | 6 => ⟨(SourceAtlas109474.demand 29).lower,(SourceAtlas109474.demand 29).defect,(SourceAtlas109474.demand 29).target⟩
  | 7 => ⟨(SourceAtlas109474.demand 157).lower,(SourceAtlas109474.demand 157).defect,(SourceAtlas109474.demand 157).target⟩
  | 8 => ⟨(SourceAtlas109474.demand 106).lower,(SourceAtlas109474.demand 106).defect,(SourceAtlas109474.demand 106).target⟩
  | 9 => ofPlan (SourceQueryData150465.query 16)
  | 10 => ofPlan (SourceQueryData150465.query 23)
  | 11 => ⟨(SourceAtlas109474.demand 38).lower,(SourceAtlas109474.demand 38).defect,(SourceAtlas109474.demand 38).target⟩
  | 12 => ofPlan (SourceQueryData130000.query 313)
  | 13 => ofPlan (SourceQueryData130000.query 321)
  | 14 => ⟨(SourceAtlas109474.demand 160).lower,(SourceAtlas109474.demand 160).defect,(SourceAtlas109474.demand 160).target⟩
  | 15 => ⟨(SourceAtlas109474.demand 188).lower,(SourceAtlas109474.demand 188).defect,(SourceAtlas109474.demand 188).target⟩
  | 16 => ⟨(SourceAtlas109474.demand 41).lower,(SourceAtlas109474.demand 41).defect,(SourceAtlas109474.demand 41).target⟩
  | _ => ofPlan (SourceQueryData130000.query 0)

def hybridPlan (i : ℕ) : CorrelatedSource109474.Plan := SourceQueryData94488.query (140+i)

def highIndex (i : ℕ) : ℕ :=
  match i with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 26
  | 10 => 27
  | 11 => 28
  | 12 => 29
  | 13 => 39
  | 14 => 40
  | 15 => 41
  | 16 => 42
  | 17 => 43
  | 18 => 50
  | 19 => 51
  | 20 => 52
  | 21 => 57
  | 22 => 60
  | 23 => 61
  | 24 => 62
  | 25 => 67
  | 26 => 68
  | 27 => 69
  | _ => 0

def HybridValid (i : ℕ) : Prop :=
  highIndex i < 70 ∧
  (RunPlans94488.plan (highIndex i)).lower ≤ (hybridPlan i).lower ∧
  (RunPlans94488.plan (highIndex i)).defect ≤ (hybridPlan i).cutoff ∧
  (hybridPlan i).target ≤ (RunPlans94488.plan (highIndex i)).target

instance (i : ℕ) : Decidable (HybridValid i) := by unfold HybridValid; infer_instance

theorem hybrid_checked : (List.range 28).all (fun i => decide (HybridValid i)) = true := by decide +kernel

theorem hybrid_valid {i : ℕ} (hi : i < 28) : HybridValid i :=
  of_decide_eq_true (List.all_eq_true.mp hybrid_checked i (List.mem_range.mpr hi))

theorem hybrid_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 28)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (hybridPlan i).lower ≤ S.card) (hdefect : (hybridPlan i).defect ≤ Defect S) :
    (hybridPlan i).target ≤ (Pool S).card := by
  have hl := hybrid_valid hi
  apply CorrelatedSource109474.actual_plan_source_of_high (hybridPlan i)
    (SourceQueryData94488.conditions (i := 140+i) (by omega)) hN hground hS hsize hdefect
  intro hhigh
  have hb := RunSource109474.actual_run_plan_source (RunPlans94488.plan (highIndex i))
    (RunFacts94488.conditions hl.1) (SourceRunFloors94488.floors hl.1) hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hhigh)
  exact hl.2.2.2.trans hb

def demand (i : ℕ) : Contract := (([⟨93,1,2375⟩, ⟨93,2,4616⟩, ⟨129,1,4616⟩, ⟨93,4,8760⟩, ⟨176,1,8760⟩, ⟨93,6,12567⟩, ⟨186,2,12567⟩, ⟨210,1,12567⟩, ⟨93,8,15928⟩, ⟨186,2,15928⟩, ⟨236,1,15928⟩, ⟨93,10,18908⟩, ⟨186,2,18908⟩, ⟨264,1,18908⟩, ⟨93,13,22705⟩, ⟨186,3,22705⟩, ⟨288,1,22705⟩, ⟨93,16,25924⟩, ⟨186,3,25924⟩, ⟨307,1,25924⟩, ⟨93,19,28478⟩, ⟨186,3,28478⟩, ⟨321,1,28478⟩, ⟨93,22,30413⟩, ⟨186,4,30413⟩, ⟨331,1,30413⟩, ⟨93,26,31742⟩, ⟨186,4,31742⟩, ⟨338,1,31742⟩, ⟨93,29,32413⟩, ⟨186,4,32413⟩, ⟨342,1,32413⟩, ⟨93,36,34034⟩, ⟨162,5,34034⟩, ⟨350,1,34034⟩, ⟨93,38,37610⟩, ⟨162,6,37610⟩, ⟨367,1,37610⟩, ⟨93,40,40854⟩, ⟨162,6,40854⟩, ⟨382,1,40854⟩, ⟨93,42,44448⟩, ⟨162,7,44448⟩, ⟨398,1,44448⟩, ⟨93,44,47344⟩, ⟨162,7,47344⟩, ⟨411,1,47344⟩, ⟨93,46,49742⟩, ⟨162,8,49742⟩, ⟨421,1,49742⟩, ⟨93,48,53284⟩, ⟨162,8,53284⟩, ⟨435,1,53284⟩, ⟨93,50,55658⟩, ⟨162,9,55658⟩, ⟨444,1,55658⟩, ⟨93,51,57712⟩, ⟨162,9,57712⟩, ⟨452,1,57712⟩, ⟨93,52,58732⟩, ⟨162,9,58732⟩, ⟨456,1,58732⟩, ⟨93,53,60452⟩, ⟨162,10,60452⟩, ⟨463,1,60452⟩, ⟨93,54,61580⟩, ⟨139,15,61580⟩, ⟨279,3,61580⟩, ⟨467,1,61580⟩, ⟨93,55,63242⟩, ⟨139,15,63242⟩, ⟨279,4,63242⟩, ⟨473,1,63242⟩, ⟨93,56,64488⟩, ⟨139,16,64488⟩, ⟨279,4,64488⟩, ⟨477,1,64488⟩, ⟨93,57,66374⟩, ⟨139,16,66374⟩, ⟨279,4,66374⟩, ⟨484,1,66374⟩, ⟨93,58,67988⟩, ⟨139,17,67988⟩, ⟨279,4,67988⟩, ⟨490,1,67988⟩, ⟨93,59,69292⟩, ⟨139,17,69292⟩, ⟨279,4,69292⟩, ⟨495,1,69292⟩, ⟨94,1,2425⟩, ⟨94,4,9009⟩, ⟨179,1,9009⟩, ⟨94,9,17920⟩, ⟨188,2,17920⟩, ⟨250,1,17920⟩, ⟨94,14,24452⟩, ⟨188,3,24452⟩, ⟨298,1,24452⟩, ⟨94,19,29236⟩, ⟨188,3,29236⟩, ⟨325,1,29236⟩, ⟨94,25,32688⟩, ⟨188,4,32688⟩, ⟨343,1,32688⟩, ⟨94,39,39762⟩, ⟨164,6,39762⟩, ⟨377,1,39762⟩, ⟨94,43,46770⟩, ⟨164,7,46770⟩, ⟨408,1,46770⟩, ⟨94,46,51002⟩, ⟨164,8,51002⟩, ⟨426,1,51002⟩, ⟨94,49,55810⟩, ⟨164,9,55810⟩, ⟨445,1,55810⟩, ⟨94,51,58560⟩, ⟨164,9,58560⟩, ⟨455,1,58560⟩, ⟨94,53,61202⟩, ⟨164,10,61202⟩, ⟨465,1,61202⟩, ⟨94,55,64132⟩, ⟨141,15,64132⟩, ⟨282,3,64132⟩, ⟨476,1,64132⟩, ⟨94,57,67632⟩, ⟨141,16,67632⟩, ⟨282,4,67632⟩, ⟨489,1,67632⟩, ⟨94,59,70890⟩, ⟨141,17,70890⟩, ⟨282,4,70890⟩, ⟨500,1,70890⟩, ⟨95,1,2475⟩, ⟨95,4,9204⟩, ⟨180,1,9204⟩, ⟨95,10,19908⟩, ⟨190,2,19908⟩, ⟨270,1,19908⟩, ⟨95,18,29164⟩, ⟨190,3,29164⟩, ⟨325,1,29164⟩, ⟨95,27,34314⟩, ⟨190,4,34314⟩, ⟨351,1,34314⟩, ⟨95,40,41986⟩, ⟨166,6,41986⟩, ⟨387,1,41986⟩, ⟨95,44,48774⟩, ⟨166,7,48774⟩, ⟨417,1,48774⟩, ⟨95,48,54588⟩, ⟨166,8,54588⟩, ⟨440,1,54588⟩, ⟨95,52,61410⟩, ⟨166,9,61410⟩, ⟨466,1,61410⟩, ⟨95,56,67126⟩, ⟨142,15,67126⟩, ⟨285,4,67126⟩, ⟨487,1,67126⟩, ⟨95,59,71930⟩, ⟨142,17,71930⟩, ⟨285,4,71930⟩, ⟨503,1,71930⟩, ⟨96,1,2529⟩, ⟨96,4,9401⟩, ⟨182,1,9401⟩, ⟨96,10,20370⟩, ⟨192,2,20370⟩, ⟨273,1,20370⟩, ⟨96,18,29912⟩, ⟨192,3,29912⟩, ⟨329,1,29912⟩, ⟨96,27,35303⟩, ⟨192,4,35303⟩, ⟨356,1,35303⟩, ⟨96,41,44258⟩, ⟨168,6,44258⟩, ⟨397,1,44258⟩, ⟨96,45,51146⟩, ⟨168,7,51146⟩, ⟨426,1,51146⟩, ⟨96,49,57624⟩, ⟨168,8,57624⟩, ⟨452,1,57624⟩, ⟨96,53,64160⟩, ⟨168,9,64160⟩, ⟨476,1,64160⟩, ⟨96,57,69896⟩, ⟨144,16,69896⟩, ⟨288,4,69896⟩, ⟨497,1,69896⟩, ⟨96,60,75086⟩, ⟨144,17,75086⟩, ⟨288,4,75086⟩, ⟨514,1,75086⟩, ⟨98,1,2654⟩, ⟨98,14,27100⟩, ⟨196,3,27100⟩, ⟨313,1,27100⟩, ⟨98,27,37325⟩, ⟨196,4,37325⟩, ⟨366,1,37325⟩, ⟨98,45,52688⟩, ⟨171,7,52688⟩, ⟨433,1,52688⟩, ⟨98,51,63190⟩, ⟨171,9,63190⟩, ⟨473,1,63190⟩, ⟨98,56,71018⟩, ⟨171,10,71018⟩, ⟨490,2,71018⟩, ⟨501,1,71018⟩, ⟨98,60,77660⟩, ⟨147,17,77660⟩, ⟨294,4,77660⟩, ⟨523,1,77660⟩, ⟨130,1,4732⟩, ⟨130,4,17937⟩, ⟨250,1,17937⟩, ⟨130,19,64948⟩, ⟨260,4,64948⟩, ⟨479,1,64948⟩, ⟨130,36,88468⟩, ⟨260,5,88468⟩, ⟨557,1,88468⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def provider (i : ℕ) : Provider := (([⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨3,0⟩, ⟨1,3⟩, ⟨3,1⟩, ⟨0,0⟩, ⟨1,4⟩, ⟨3,2⟩, ⟨1,5⟩, ⟨1,6⟩, ⟨3,3⟩, ⟨1,7⟩, ⟨1,8⟩, ⟨1,9⟩, ⟨1,10⟩, ⟨1,11⟩, ⟨3,4⟩, ⟨1,12⟩, ⟨1,13⟩, ⟨3,5⟩, ⟨1,14⟩, ⟨0,1⟩, ⟨3,6⟩, ⟨1,15⟩, ⟨0,2⟩, ⟨3,7⟩, ⟨1,16⟩, ⟨1,17⟩, ⟨3,8⟩, ⟨1,18⟩, ⟨0,3⟩, ⟨2,9⟩, ⟨1,19⟩, ⟨1,20⟩, ⟨2,10⟩, ⟨1,21⟩, ⟨1,22⟩, ⟨2,11⟩, ⟨1,23⟩, ⟨1,24⟩, ⟨2,12⟩, ⟨0,4⟩, ⟨1,25⟩, ⟨2,13⟩, ⟨1,26⟩, ⟨0,5⟩, ⟨2,14⟩, ⟨1,27⟩, ⟨0,6⟩, ⟨2,15⟩, ⟨1,28⟩, ⟨1,29⟩, ⟨2,16⟩, ⟨1,30⟩, ⟨1,31⟩, ⟨2,17⟩, ⟨1,32⟩, ⟨1,33⟩, ⟨2,18⟩, ⟨1,34⟩, ⟨1,35⟩, ⟨2,19⟩, ⟨1,36⟩, ⟨1,37⟩, ⟨2,20⟩, ⟨1,38⟩, ⟨1,39⟩, ⟨1,40⟩, ⟨2,21⟩, ⟨1,41⟩, ⟨1,42⟩, ⟨0,7⟩, ⟨2,22⟩, ⟨1,43⟩, ⟨1,44⟩, ⟨1,45⟩, ⟨2,23⟩, ⟨1,46⟩, ⟨1,47⟩, ⟨1,48⟩, ⟨2,24⟩, ⟨1,49⟩, ⟨1,50⟩, ⟨0,8⟩, ⟨2,25⟩, ⟨1,51⟩, ⟨1,52⟩, ⟨1,53⟩, ⟨1,54⟩, ⟨3,9⟩, ⟨1,55⟩, ⟨3,10⟩, ⟨1,56⟩, ⟨1,57⟩, ⟨1,58⟩, ⟨1,59⟩, ⟨1,60⟩, ⟨3,11⟩, ⟨1,61⟩, ⟨1,62⟩, ⟨3,12⟩, ⟨1,63⟩, ⟨1,64⟩, ⟨2,30⟩, ⟨1,65⟩, ⟨1,66⟩, ⟨2,31⟩, ⟨1,67⟩, ⟨1,68⟩, ⟨2,32⟩, ⟨0,9⟩, ⟨1,69⟩, ⟨2,33⟩, ⟨1,70⟩, ⟨1,71⟩, ⟨2,34⟩, ⟨1,72⟩, ⟨1,73⟩, ⟨2,35⟩, ⟨0,10⟩, ⟨1,74⟩, ⟨2,36⟩, ⟨1,75⟩, ⟨1,76⟩, ⟨1,77⟩, ⟨2,37⟩, ⟨1,78⟩, ⟨1,79⟩, ⟨1,80⟩, ⟨2,38⟩, ⟨1,81⟩, ⟨1,82⟩, ⟨1,83⟩, ⟨1,84⟩, ⟨3,13⟩, ⟨3,14⟩, ⟨3,15⟩, ⟨1,85⟩, ⟨1,86⟩, ⟨3,16⟩, ⟨1,87⟩, ⟨1,88⟩, ⟨3,17⟩, ⟨1,89⟩, ⟨1,90⟩, ⟨2,44⟩, ⟨1,91⟩, ⟨1,92⟩, ⟨2,45⟩, ⟨1,93⟩, ⟨1,94⟩, ⟨2,46⟩, ⟨1,95⟩, ⟨1,96⟩, ⟨2,47⟩, ⟨1,97⟩, ⟨0,11⟩, ⟨2,48⟩, ⟨1,98⟩, ⟨1,99⟩, ⟨1,100⟩, ⟨2,49⟩, ⟨1,101⟩, ⟨1,102⟩, ⟨1,103⟩, ⟨3,18⟩, ⟨1,104⟩, ⟨1,105⟩, ⟨3,19⟩, ⟨1,106⟩, ⟨1,107⟩, ⟨1,108⟩, ⟨1,109⟩, ⟨1,110⟩, ⟨3,20⟩, ⟨1,111⟩, ⟨1,112⟩, ⟨2,53⟩, ⟨1,113⟩, ⟨1,114⟩, ⟨2,54⟩, ⟨1,115⟩, ⟨1,116⟩, ⟨2,55⟩, ⟨1,117⟩, ⟨1,118⟩, ⟨2,56⟩, ⟨3,21⟩, ⟨1,119⟩, ⟨2,58⟩, ⟨1,120⟩, ⟨1,121⟩, ⟨1,122⟩, ⟨2,59⟩, ⟨1,123⟩, ⟨1,124⟩, ⟨1,125⟩, ⟨3,22⟩, ⟨3,23⟩, ⟨1,126⟩, ⟨1,127⟩, ⟨3,24⟩, ⟨0,12⟩, ⟨1,128⟩, ⟨2,63⟩, ⟨1,129⟩, ⟨1,130⟩, ⟨2,64⟩, ⟨1,131⟩, ⟨0,7⟩, ⟨2,65⟩, ⟨1,132⟩, ⟨0,13⟩, ⟨0,14⟩, ⟨2,66⟩, ⟨1,133⟩, ⟨1,134⟩, ⟨1,135⟩, ⟨0,15⟩, ⟨3,25⟩, ⟨1,136⟩, ⟨3,26⟩, ⟨1,137⟩, ⟨0,16⟩, ⟨3,27⟩, ⟨1,138⟩, ⟨1,139⟩] : List Provider)[i]?).getD ⟨0,0⟩

def reference (i : ℕ) : Contract :=
  if (provider i).kind=0 then oldContract (provider i).index else
  if (provider i).kind=1 then ofPlan (SourceQueryData94488.query (provider i).index) else
  if (provider i).kind=2 then ofRun (RunPlans94488.plan (provider i).index) else
    ofPlan (hybridPlan (provider i).index)

def capacity (kind : ℕ) : ℕ := if kind=0 then 17 else if kind=1 then 140 else if kind=2 then 70 else 28

def Valid (i : ℕ) : Prop :=
  (provider i).kind < 4 ∧ (provider i).index < capacity (provider i).kind ∧
  (reference i).lower ≤ (demand i).lower ∧
  (reference i).defect ≤ (demand i).defect ∧ (demand i).target ≤ (reference i).target

instance (i : ℕ) : Decidable (Valid i) := by unfold Valid; infer_instance

theorem checked0 : (List.range 16).all (fun j => decide (Valid (0+j))) = true := by decide +kernel
#print axioms checked0

theorem piece0 {i : ℕ} (hlo : 0 ≤ i) (hhi : i < 16) : Valid i := by
  have hm : i-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked0 (i-0) hm)
  have he : 0+(i-0) = i := by omega
  simpa only [he] using hc
#print axioms piece0

theorem checked1 : (List.range 16).all (fun j => decide (Valid (16+j))) = true := by decide +kernel
#print axioms checked1

theorem piece1 {i : ℕ} (hlo : 16 ≤ i) (hhi : i < 32) : Valid i := by
  have hm : i-16 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked1 (i-16) hm)
  have he : 16+(i-16) = i := by omega
  simpa only [he] using hc
#print axioms piece1

theorem checked2 : (List.range 16).all (fun j => decide (Valid (32+j))) = true := by decide +kernel
#print axioms checked2

theorem piece2 {i : ℕ} (hlo : 32 ≤ i) (hhi : i < 48) : Valid i := by
  have hm : i-32 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked2 (i-32) hm)
  have he : 32+(i-32) = i := by omega
  simpa only [he] using hc
#print axioms piece2

theorem checked3 : (List.range 16).all (fun j => decide (Valid (48+j))) = true := by decide +kernel
#print axioms checked3

theorem piece3 {i : ℕ} (hlo : 48 ≤ i) (hhi : i < 64) : Valid i := by
  have hm : i-48 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked3 (i-48) hm)
  have he : 48+(i-48) = i := by omega
  simpa only [he] using hc
#print axioms piece3

theorem checked4 : (List.range 16).all (fun j => decide (Valid (64+j))) = true := by decide +kernel
#print axioms checked4

theorem piece4 {i : ℕ} (hlo : 64 ≤ i) (hhi : i < 80) : Valid i := by
  have hm : i-64 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked4 (i-64) hm)
  have he : 64+(i-64) = i := by omega
  simpa only [he] using hc
#print axioms piece4

theorem checked5 : (List.range 16).all (fun j => decide (Valid (80+j))) = true := by decide +kernel
#print axioms checked5

theorem piece5 {i : ℕ} (hlo : 80 ≤ i) (hhi : i < 96) : Valid i := by
  have hm : i-80 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked5 (i-80) hm)
  have he : 80+(i-80) = i := by omega
  simpa only [he] using hc
#print axioms piece5

theorem checked6 : (List.range 16).all (fun j => decide (Valid (96+j))) = true := by decide +kernel
#print axioms checked6

theorem piece6 {i : ℕ} (hlo : 96 ≤ i) (hhi : i < 112) : Valid i := by
  have hm : i-96 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked6 (i-96) hm)
  have he : 96+(i-96) = i := by omega
  simpa only [he] using hc
#print axioms piece6

theorem checked7 : (List.range 16).all (fun j => decide (Valid (112+j))) = true := by decide +kernel
#print axioms checked7

theorem piece7 {i : ℕ} (hlo : 112 ≤ i) (hhi : i < 128) : Valid i := by
  have hm : i-112 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked7 (i-112) hm)
  have he : 112+(i-112) = i := by omega
  simpa only [he] using hc
#print axioms piece7

theorem checked8 : (List.range 16).all (fun j => decide (Valid (128+j))) = true := by decide +kernel
#print axioms checked8

theorem piece8 {i : ℕ} (hlo : 128 ≤ i) (hhi : i < 144) : Valid i := by
  have hm : i-128 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked8 (i-128) hm)
  have he : 128+(i-128) = i := by omega
  simpa only [he] using hc
#print axioms piece8

theorem checked9 : (List.range 16).all (fun j => decide (Valid (144+j))) = true := by decide +kernel
#print axioms checked9

theorem piece9 {i : ℕ} (hlo : 144 ≤ i) (hhi : i < 160) : Valid i := by
  have hm : i-144 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked9 (i-144) hm)
  have he : 144+(i-144) = i := by omega
  simpa only [he] using hc
#print axioms piece9

theorem checked10 : (List.range 16).all (fun j => decide (Valid (160+j))) = true := by decide +kernel
#print axioms checked10

theorem piece10 {i : ℕ} (hlo : 160 ≤ i) (hhi : i < 176) : Valid i := by
  have hm : i-160 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked10 (i-160) hm)
  have he : 160+(i-160) = i := by omega
  simpa only [he] using hc
#print axioms piece10

theorem checked11 : (List.range 16).all (fun j => decide (Valid (176+j))) = true := by decide +kernel
#print axioms checked11

theorem piece11 {i : ℕ} (hlo : 176 ≤ i) (hhi : i < 192) : Valid i := by
  have hm : i-176 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked11 (i-176) hm)
  have he : 176+(i-176) = i := by omega
  simpa only [he] using hc
#print axioms piece11

theorem checked12 : (List.range 16).all (fun j => decide (Valid (192+j))) = true := by decide +kernel
#print axioms checked12

theorem piece12 {i : ℕ} (hlo : 192 ≤ i) (hhi : i < 208) : Valid i := by
  have hm : i-192 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked12 (i-192) hm)
  have he : 192+(i-192) = i := by omega
  simpa only [he] using hc
#print axioms piece12

theorem checked13 : (List.range 16).all (fun j => decide (Valid (208+j))) = true := by decide +kernel
#print axioms checked13

theorem piece13 {i : ℕ} (hlo : 208 ≤ i) (hhi : i < 224) : Valid i := by
  have hm : i-208 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked13 (i-208) hm)
  have he : 208+(i-208) = i := by omega
  simpa only [he] using hc
#print axioms piece13

theorem checked14 : (List.range 4).all (fun j => decide (Valid (224+j))) = true := by decide +kernel
#print axioms checked14

theorem piece14 {i : ℕ} (hlo : 224 ≤ i) (hhi : i < 228) : Valid i := by
  have hm : i-224 ∈ List.range 4 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked14 (i-224) hm)
  have he : 224+(i-224) = i := by omega
  simpa only [he] using hc
#print axioms piece14

theorem valid {i : ℕ} (hi : i < 228) : Valid i := by
  by_cases h0 : i < 16
  · exact piece0 (by omega) h0
  by_cases h1 : i < 32
  · exact piece1 (by omega) h1
  by_cases h2 : i < 48
  · exact piece2 (by omega) h2
  by_cases h3 : i < 64
  · exact piece3 (by omega) h3
  by_cases h4 : i < 80
  · exact piece4 (by omega) h4
  by_cases h5 : i < 96
  · exact piece5 (by omega) h5
  by_cases h6 : i < 112
  · exact piece6 (by omega) h6
  by_cases h7 : i < 128
  · exact piece7 (by omega) h7
  by_cases h8 : i < 144
  · exact piece8 (by omega) h8
  by_cases h9 : i < 160
  · exact piece9 (by omega) h9
  by_cases h10 : i < 176
  · exact piece10 (by omega) h10
  by_cases h11 : i < 192
  · exact piece11 (by omega) h11
  by_cases h12 : i < 208
  · exact piece12 (by omega) h12
  by_cases h13 : i < 224
  · exact piece13 (by omega) h13
  exact piece14 (by omega) hi

theorem old_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 17)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (oldContract i).lower ≤ S.card) (hdefect : (oldContract i).defect ≤ Defect S) :
    (oldContract i).target ≤ (Pool S).card := by
  interval_cases i
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 122)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 11) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 17)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 142) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 136)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 151) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 29) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 157) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 106) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData150465.query 16)
      (SourceQueryData150465.conditions (by decide)) (RowSources150465.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData150465.query 23)
      (SourceQueryData150465.conditions (by decide)) (RowSources150465.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 38) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 313)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 321)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 160) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 188) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 41) (by decide)
      hN hground hS hsize hdefect

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 228)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hv := valid hi
  have hl := hv.2.2.1.trans hsize
  have he := hv.2.2.2.1.trans hdefect
  by_cases h0 : (provider i).kind=0
  · have hb := old_actual (i := (provider i).index)
      (by simpa [capacity, h0] using hv.2.1) hN hground hS
      (by simpa [reference, h0] using hl) (by simpa [reference, h0] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0] using hb)
  by_cases h1 : (provider i).kind=1
  · have hiq : (provider i).index < 140 := by simpa [capacity, h1] using hv.2.1
    have hb := CorrelatedSource118533.actual_plan_source (SourceQueryData94488.query (provider i).index)
      (SourceQueryData94488.conditions (by omega : (provider i).index < 168))
      (SourceQueryFloors94488.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, ofPlan] using hl)
      (by simpa [reference, h0, h1, ofPlan] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, ofPlan] using hb)
  by_cases h2 : (provider i).kind=2
  · have hiq : (provider i).index < 70 := by simpa [capacity, h2] using hv.2.1
    have hb := RunSource109474.actual_run_plan_source (RunPlans94488.plan (provider i).index)
      (RunFacts94488.conditions hiq) (SourceRunFloors94488.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, h2, ofRun] using hl)
      (by simpa [reference, h0, h1, h2, ofRun] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, h2, ofRun] using hb)
  have hiq : (provider i).index < 28 := by simpa [capacity, h0, h1, h2] using hv.2.1
  have hb := hybrid_actual hiq hN hground hS
    (by simpa [reference, h0, h1, h2, ofPlan] using hl)
    (by simpa [reference, h0, h1, h2, ofPlan] using he)
  exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, h2, ofPlan] using hb)

#print axioms hybrid_checked
#print axioms hybrid_valid
#print axioms hybrid_actual
#print axioms valid
#print axioms old_actual
#print axioms actual_source
end
end JSP233.SourceAtlas94488
