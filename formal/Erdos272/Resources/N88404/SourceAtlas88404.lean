module

public import Erdos272.Arithmetic.N88404.SourceQueryFloors88404
public import Erdos272.Arithmetic.N88404.SourceRunFloors88404
public import Erdos272.Counting.N88404.RunFacts88404
public import Erdos272.Resources.N109474.RunSource109474
public import Erdos272.Resources.N109474.CorrelatedSource109474
public import Erdos272.Resources.N142758.RowSources142758
public import Erdos272.Resources.N158375.RowSources158375
public import Erdos272.Resources.N109474.SourceAtlas109474
public import Erdos272.Resources.N94488.SourceAtlas94488

@[expose] public section

namespace JSP233.SourceAtlas88404
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
  | 1 => ofPlan (SourceQueryData158375.query 2)
  | 2 => ⟨(SourceAtlas94488.demand 22).lower,(SourceAtlas94488.demand 22).defect,(SourceAtlas94488.demand 22).target⟩
  | 3 => ⟨(SourceAtlas94488.demand 100).lower,(SourceAtlas94488.demand 100).defect,(SourceAtlas94488.demand 100).target⟩
  | 4 => ⟨(SourceAtlas109474.demand 151).lower,(SourceAtlas109474.demand 151).defect,(SourceAtlas109474.demand 151).target⟩
  | 5 => ⟨(SourceAtlas109474.demand 29).lower,(SourceAtlas109474.demand 29).defect,(SourceAtlas109474.demand 29).target⟩
  | 6 => ⟨(SourceAtlas94488.demand 55).lower,(SourceAtlas94488.demand 55).defect,(SourceAtlas94488.demand 55).target⟩
  | 7 => ⟨(SourceAtlas109474.demand 35).lower,(SourceAtlas109474.demand 35).defect,(SourceAtlas109474.demand 35).target⟩
  | 8 => ⟨(SourceAtlas94488.demand 223).lower,(SourceAtlas94488.demand 223).defect,(SourceAtlas94488.demand 223).target⟩
  | 9 => ⟨(SourceAtlas94488.demand 157).lower,(SourceAtlas94488.demand 157).defect,(SourceAtlas94488.demand 157).target⟩
  | 10 => ⟨(SourceAtlas94488.demand 16).lower,(SourceAtlas94488.demand 16).defect,(SourceAtlas94488.demand 16).target⟩
  | 11 => ⟨(SourceAtlas94488.demand 201).lower,(SourceAtlas94488.demand 201).defect,(SourceAtlas94488.demand 201).target⟩
  | 12 => ⟨(SourceAtlas94488.demand 25).lower,(SourceAtlas94488.demand 25).defect,(SourceAtlas94488.demand 25).target⟩
  | 13 => ofPlan (SourceQueryData142758.query 23)
  | 14 => ⟨(SourceAtlas109474.demand 26).lower,(SourceAtlas109474.demand 26).defect,(SourceAtlas109474.demand 26).target⟩
  | 15 => ⟨(SourceAtlas94488.demand 125).lower,(SourceAtlas94488.demand 125).defect,(SourceAtlas94488.demand 125).target⟩
  | 16 => ⟨(SourceAtlas94488.demand 139).lower,(SourceAtlas94488.demand 139).defect,(SourceAtlas94488.demand 139).target⟩
  | 17 => ofPlan (SourceQueryData142758.query 136)
  | 18 => ⟨(SourceAtlas94488.demand 224).lower,(SourceAtlas94488.demand 224).defect,(SourceAtlas94488.demand 224).target⟩
  | 19 => ⟨(SourceAtlas94488.demand 219).lower,(SourceAtlas94488.demand 219).defect,(SourceAtlas94488.demand 219).target⟩
  | 20 => ⟨(SourceAtlas94488.demand 220).lower,(SourceAtlas94488.demand 220).defect,(SourceAtlas94488.demand 220).target⟩
  | 21 => ⟨(SourceAtlas94488.demand 221).lower,(SourceAtlas94488.demand 221).defect,(SourceAtlas94488.demand 221).target⟩
  | 22 => ⟨(SourceAtlas94488.demand 222).lower,(SourceAtlas94488.demand 222).defect,(SourceAtlas94488.demand 222).target⟩
  | 23 => ⟨(SourceAtlas94488.demand 225).lower,(SourceAtlas94488.demand 225).defect,(SourceAtlas94488.demand 225).target⟩
  | 24 => ⟨(SourceAtlas94488.demand 226).lower,(SourceAtlas94488.demand 226).defect,(SourceAtlas94488.demand 226).target⟩
  | 25 => ⟨(SourceAtlas94488.demand 227).lower,(SourceAtlas94488.demand 227).defect,(SourceAtlas94488.demand 227).target⟩
  | _ => ofPlan (SourceQueryData130000.query 0)

def hybridPlan (i : ℕ) : CorrelatedSource109474.Plan := SourceQueryData88404.query (138+i)

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
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | 16 => 16
  | 17 => 17
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 21
  | 22 => 22
  | 23 => 45
  | 24 => 48
  | 25 => 49
  | 26 => 50
  | 27 => 51
  | 28 => 63
  | 29 => 64
  | 30 => 65
  | 31 => 66
  | 32 => 67
  | 33 => 68
  | _ => 0

def HybridValid (i : ℕ) : Prop :=
  highIndex i < 75 ∧
  (RunPlans88404.plan (highIndex i)).lower ≤ (hybridPlan i).lower ∧
  (RunPlans88404.plan (highIndex i)).defect ≤ (hybridPlan i).cutoff ∧
  (hybridPlan i).target ≤ (RunPlans88404.plan (highIndex i)).target

instance (i : ℕ) : Decidable (HybridValid i) := by unfold HybridValid; infer_instance

theorem hybrid_checked : (List.range 34).all (fun i => decide (HybridValid i)) = true := by decide +kernel

theorem hybrid_valid {i : ℕ} (hi : i < 34) : HybridValid i :=
  of_decide_eq_true (List.all_eq_true.mp hybrid_checked i (List.mem_range.mpr hi))

theorem hybrid_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 34)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (hybridPlan i).lower ≤ S.card) (hdefect : (hybridPlan i).defect ≤ Defect S) :
    (hybridPlan i).target ≤ (Pool S).card := by
  have hl := hybrid_valid hi
  apply CorrelatedSource109474.actual_plan_source_of_high (hybridPlan i)
    (SourceQueryData88404.conditions (i := 138+i) (by omega)) hN hground hS hsize hdefect
  intro hhigh
  have hb := RunSource109474.actual_run_plan_source (RunPlans88404.plan (highIndex i))
    (RunFacts88404.conditions hl.1) (SourceRunFloors88404.floors hl.1) hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hhigh)
  exact hl.2.2.2.trans hb

def demand (i : ℕ) : Contract := (([⟨90,1,2211⟩, ⟨90,2,4313⟩, ⟨125,1,4313⟩, ⟨90,3,6286⟩, ⟨150,1,6286⟩, ⟨90,4,8192⟩, ⟨171,1,8192⟩, ⟨90,5,10010⟩, ⟨180,2,10010⟩, ⟨188,1,10010⟩, ⟨90,6,11674⟩, ⟨180,2,11674⟩, ⟨203,1,11674⟩, ⟨90,7,13236⟩, ⟨180,2,13236⟩, ⟨216,1,13236⟩, ⟨90,8,14764⟩, ⟨180,2,14764⟩, ⟨228,1,14764⟩, ⟨90,9,16216⟩, ⟨180,2,16216⟩, ⟨238,1,16216⟩, ⟨90,10,17554⟩, ⟨180,2,17554⟩, ⟨248,1,17554⟩, ⟨90,11,18743⟩, ⟨180,3,18743⟩, ⟨262,1,18743⟩, ⟨90,12,19941⟩, ⟨180,3,19941⟩, ⟨270,1,19941⟩, ⟨90,13,21063⟩, ⟨180,3,21063⟩, ⟨278,1,21063⟩, ⟨90,14,22109⟩, ⟨180,3,22109⟩, ⟨284,1,22109⟩, ⟨90,15,23081⟩, ⟨180,3,23081⟩, ⟨290,1,23081⟩, ⟨90,16,23981⟩, ⟨180,3,23981⟩, ⟨296,1,23981⟩, ⟨90,17,24811⟩, ⟨180,3,24811⟩, ⟨300,1,24811⟩, ⟨90,18,25320⟩, ⟨180,3,25320⟩, ⟨303,1,25320⟩, ⟨90,19,26000⟩, ⟨180,3,26000⟩, ⟨307,1,26000⟩, ⟨90,20,26614⟩, ⟨180,3,26614⟩, ⟨311,1,26614⟩, ⟨90,21,27164⟩, ⟨180,4,27164⟩, ⟨314,1,27164⟩, ⟨90,22,27652⟩, ⟨180,4,27652⟩, ⟨317,1,27652⟩, ⟨90,23,28079⟩, ⟨180,4,28079⟩, ⟨319,1,28079⟩, ⟨90,24,28447⟩, ⟨180,4,28447⟩, ⟨321,1,28447⟩, ⟨90,25,28758⟩, ⟨180,4,28758⟩, ⟨323,1,28758⟩, ⟨90,26,29168⟩, ⟨180,4,29168⟩, ⟨325,1,29168⟩, ⟨90,27,29371⟩, ⟨180,4,29371⟩, ⟨326,1,29371⟩, ⟨90,28,29523⟩, ⟨180,4,29523⟩, ⟨327,1,29523⟩, ⟨90,29,29548⟩, ⟨180,4,29548⟩, ⟨327,1,29548⟩, ⟨90,34,29664⟩, ⟨157,5,29664⟩, ⟨327,1,29664⟩, ⟨90,35,31526⟩, ⟨157,5,31526⟩, ⟨337,1,31526⟩, ⟨90,36,32978⟩, ⟨157,6,32978⟩, ⟨345,1,32978⟩, ⟨90,37,34606⟩, ⟨157,6,34606⟩, ⟨353,1,34606⟩, ⟨90,38,35822⟩, ⟨157,6,35822⟩, ⟨359,1,35822⟩, ⟨90,39,37854⟩, ⟨157,6,37854⟩, ⟨368,1,37854⟩, ⟨90,40,39196⟩, ⟨157,7,39196⟩, ⟨375,1,39196⟩, ⟨90,41,41164⟩, ⟨157,7,41164⟩, ⟨384,1,41164⟩, ⟨90,42,41790⟩, ⟨157,7,41790⟩, ⟨386,1,41790⟩, ⟨90,43,43656⟩, ⟨157,7,43656⟩, ⟨395,1,43656⟩, ⟨90,44,44770⟩, ⟨157,8,44770⟩, ⟨399,1,44770⟩, ⟨90,45,45160⟩, ⟨157,8,45160⟩, ⟨401,1,45160⟩, ⟨90,46,47548⟩, ⟨157,8,47548⟩, ⟨411,1,47548⟩, ⟨90,47,49168⟩, ⟨157,8,49168⟩, ⟨418,1,49168⟩, ⟨90,48,49794⟩, ⟨157,8,49794⟩, ⟨421,1,49794⟩, ⟨90,49,51738⟩, ⟨157,9,51738⟩, ⟨429,1,51738⟩, ⟨90,50,52900⟩, ⟨157,9,52900⟩, ⟨434,1,52900⟩, ⟨90,51,54238⟩, ⟨157,9,54238⟩, ⟨439,1,54238⟩, ⟨90,52,55630⟩, ⟨157,10,55630⟩, ⟨444,1,55630⟩, ⟨90,53,57032⟩, ⟨157,10,57032⟩, ⟨450,1,57032⟩, ⟨90,54,57856⟩, ⟨135,15,57856⟩, ⟨270,3,57856⟩, ⟨453,1,57856⟩, ⟨90,55,60062⟩, ⟨135,15,60062⟩, ⟨270,4,60062⟩, ⟨461,1,60062⟩, ⟨90,56,61406⟩, ⟨135,16,61406⟩, ⟨270,4,61406⟩, ⟨466,1,61406⟩, ⟨90,57,62624⟩, ⟨135,16,62624⟩, ⟨270,4,62624⟩, ⟨471,1,62624⟩, ⟨91,1,2259⟩, ⟨91,4,8378⟩, ⟨172,1,8378⟩, ⟨91,9,16610⟩, ⟨182,2,16610⟩, ⟨241,1,16610⟩, ⟨91,14,22683⟩, ⟨182,3,22683⟩, ⟨288,1,22683⟩, ⟨91,19,26993⟩, ⟨182,3,26993⟩, ⟨313,1,26993⟩, ⟨91,27,30289⟩, ⟨182,4,30289⟩, ⟨331,1,30289⟩, ⟨91,36,33494⟩, ⟨159,5,33494⟩, ⟨347,1,33494⟩, ⟨91,38,36606⟩, ⟨159,6,36606⟩, ⟨362,1,36606⟩, ⟨91,40,39992⟩, ⟨159,7,39992⟩, ⟨378,1,39992⟩, ⟨91,42,43024⟩, ⟨159,7,43024⟩, ⟨392,1,43024⟩, ⟨91,44,45830⟩, ⟨159,8,45830⟩, ⟨404,1,45830⟩, ⟨91,47,50078⟩, ⟨159,8,50078⟩, ⟨422,1,50078⟩, ⟨91,50,54268⟩, ⟨159,9,54268⟩, ⟨439,1,54268⟩, ⟨91,52,56820⟩, ⟨159,9,56820⟩, ⟨449,1,56820⟩, ⟨91,54,59548⟩, ⟨136,15,59548⟩, ⟨273,3,59548⟩, ⟨459,1,59548⟩, ⟨91,56,62278⟩, ⟨136,16,62278⟩, ⟨273,4,62278⟩, ⟨469,1,62278⟩, ⟨91,57,64130⟩, ⟨136,16,64130⟩, ⟨273,4,64130⟩, ⟨476,1,64130⟩, ⟨92,1,2326⟩, ⟨92,4,8570⟩, ⟨174,1,8570⟩, ⟨92,11,19819⟩, ⟨184,3,19819⟩, ⟨270,1,19819⟩, ⟨92,19,27730⟩, ⟨184,3,27730⟩, ⟨317,1,27730⟩, ⟨92,28,31411⟩, ⟨184,4,31411⟩, ⟨337,1,31411⟩, ⟨92,39,38712⟩, ⟨161,6,38712⟩, ⟨372,1,38712⟩, ⟨92,43,44796⟩, ⟨161,7,44796⟩, ⟨400,1,44796⟩, ⟨92,47,50768⟩, ⟨161,8,50768⟩, ⟨425,1,50768⟩, ⟨92,51,56698⟩, ⟨161,9,56698⟩, ⟨448,1,56698⟩, ⟨92,53,59368⟩, ⟨161,10,59368⟩, ⟨458,1,59368⟩, ⟨92,57,64934⟩, ⟨138,16,64934⟩, ⟨276,4,64934⟩, ⟨479,1,64934⟩, ⟨130,1,4732⟩, ⟨130,4,17937⟩, ⟨250,1,17937⟩, ⟨130,19,64948⟩, ⟨260,4,64948⟩, ⟨479,1,64948⟩, ⟨130,36,88468⟩, ⟨260,5,88468⟩, ⟨557,1,88468⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def provider (i : ℕ) : Provider := (([⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨3,0⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨3,1⟩, ⟨0,0⟩, ⟨1,6⟩, ⟨3,2⟩, ⟨0,0⟩, ⟨1,7⟩, ⟨3,3⟩, ⟨0,0⟩, ⟨1,8⟩, ⟨3,4⟩, ⟨0,1⟩, ⟨1,9⟩, ⟨3,5⟩, ⟨1,10⟩, ⟨1,11⟩, ⟨3,6⟩, ⟨1,12⟩, ⟨1,13⟩, ⟨1,14⟩, ⟨1,15⟩, ⟨1,16⟩, ⟨1,17⟩, ⟨1,18⟩, ⟨1,19⟩, ⟨3,7⟩, ⟨1,20⟩, ⟨1,21⟩, ⟨3,8⟩, ⟨1,22⟩, ⟨1,23⟩, ⟨3,9⟩, ⟨1,24⟩, ⟨1,25⟩, ⟨3,10⟩, ⟨1,26⟩, ⟨1,27⟩, ⟨3,11⟩, ⟨1,28⟩, ⟨1,29⟩, ⟨1,30⟩, ⟨1,31⟩, ⟨1,32⟩, ⟨3,12⟩, ⟨1,33⟩, ⟨1,34⟩, ⟨3,13⟩, ⟨1,35⟩, ⟨1,36⟩, ⟨3,14⟩, ⟨1,37⟩, ⟨1,38⟩, ⟨3,15⟩, ⟨1,39⟩, ⟨1,40⟩, ⟨3,16⟩, ⟨1,41⟩, ⟨1,42⟩, ⟨3,17⟩, ⟨1,43⟩, ⟨0,2⟩, ⟨3,18⟩, ⟨1,44⟩, ⟨1,45⟩, ⟨3,19⟩, ⟨1,46⟩, ⟨0,3⟩, ⟨3,20⟩, ⟨1,47⟩, ⟨1,48⟩, ⟨3,21⟩, ⟨1,49⟩, ⟨1,50⟩, ⟨3,22⟩, ⟨1,51⟩, ⟨1,52⟩, ⟨2,23⟩, ⟨1,53⟩, ⟨1,54⟩, ⟨2,24⟩, ⟨1,55⟩, ⟨1,56⟩, ⟨2,25⟩, ⟨1,57⟩, ⟨1,58⟩, ⟨2,26⟩, ⟨1,59⟩, ⟨1,60⟩, ⟨2,27⟩, ⟨1,61⟩, ⟨1,62⟩, ⟨2,28⟩, ⟨1,63⟩, ⟨1,64⟩, ⟨2,29⟩, ⟨1,65⟩, ⟨1,66⟩, ⟨2,30⟩, ⟨1,67⟩, ⟨1,68⟩, ⟨2,31⟩, ⟨1,69⟩, ⟨1,70⟩, ⟨2,32⟩, ⟨1,71⟩, ⟨1,72⟩, ⟨2,33⟩, ⟨1,73⟩, ⟨1,74⟩, ⟨2,34⟩, ⟨1,75⟩, ⟨1,76⟩, ⟨2,35⟩, ⟨1,77⟩, ⟨0,4⟩, ⟨2,36⟩, ⟨1,78⟩, ⟨1,79⟩, ⟨2,37⟩, ⟨1,80⟩, ⟨0,5⟩, ⟨2,38⟩, ⟨1,81⟩, ⟨1,82⟩, ⟨2,39⟩, ⟨1,83⟩, ⟨1,84⟩, ⟨2,40⟩, ⟨1,85⟩, ⟨1,86⟩, ⟨2,41⟩, ⟨1,87⟩, ⟨0,6⟩, ⟨2,42⟩, ⟨1,88⟩, ⟨1,89⟩, ⟨2,43⟩, ⟨1,90⟩, ⟨1,91⟩, ⟨0,7⟩, ⟨2,44⟩, ⟨3,23⟩, ⟨0,8⟩, ⟨1,92⟩, ⟨2,46⟩, ⟨1,93⟩, ⟨0,8⟩, ⟨0,9⟩, ⟨2,47⟩, ⟨1,94⟩, ⟨0,8⟩, ⟨1,95⟩, ⟨1,96⟩, ⟨1,97⟩, ⟨1,98⟩, ⟨3,24⟩, ⟨1,99⟩, ⟨1,100⟩, ⟨3,25⟩, ⟨1,101⟩, ⟨0,10⟩, ⟨3,26⟩, ⟨1,102⟩, ⟨0,11⟩, ⟨3,27⟩, ⟨1,103⟩, ⟨0,12⟩, ⟨2,52⟩, ⟨1,104⟩, ⟨1,105⟩, ⟨2,53⟩, ⟨1,106⟩, ⟨1,107⟩, ⟨2,54⟩, ⟨0,13⟩, ⟨1,108⟩, ⟨2,55⟩, ⟨0,13⟩, ⟨1,109⟩, ⟨2,56⟩, ⟨1,110⟩, ⟨0,14⟩, ⟨2,57⟩, ⟨1,111⟩, ⟨1,112⟩, ⟨2,58⟩, ⟨1,113⟩, ⟨1,114⟩, ⟨2,59⟩, ⟨1,115⟩, ⟨1,116⟩, ⟨2,60⟩, ⟨1,117⟩, ⟨1,118⟩, ⟨1,119⟩, ⟨2,61⟩, ⟨1,120⟩, ⟨0,8⟩, ⟨1,121⟩, ⟨2,62⟩, ⟨3,28⟩, ⟨0,8⟩, ⟨0,15⟩, ⟨3,29⟩, ⟨3,30⟩, ⟨1,122⟩, ⟨3,31⟩, ⟨1,123⟩, ⟨0,16⟩, ⟨3,32⟩, ⟨1,124⟩, ⟨1,125⟩, ⟨3,33⟩, ⟨1,126⟩, ⟨1,127⟩, ⟨2,69⟩, ⟨1,128⟩, ⟨1,129⟩, ⟨2,70⟩, ⟨0,17⟩, ⟨1,130⟩, ⟨2,71⟩, ⟨1,131⟩, ⟨1,132⟩, ⟨2,72⟩, ⟨1,133⟩, ⟨1,134⟩, ⟨2,73⟩, ⟨1,135⟩, ⟨1,136⟩, ⟨2,74⟩, ⟨1,137⟩, ⟨0,8⟩, ⟨0,18⟩, ⟨0,19⟩, ⟨0,20⟩, ⟨0,21⟩, ⟨0,22⟩, ⟨0,8⟩, ⟨0,18⟩, ⟨0,23⟩, ⟨0,24⟩, ⟨0,25⟩] : List Provider)[i]?).getD ⟨0,0⟩

def reference (i : ℕ) : Contract :=
  if (provider i).kind=0 then oldContract (provider i).index else
  if (provider i).kind=1 then ofPlan (SourceQueryData88404.query (provider i).index) else
  if (provider i).kind=2 then ofRun (RunPlans88404.plan (provider i).index) else
    ofPlan (hybridPlan (provider i).index)

def capacity (kind : ℕ) : ℕ := if kind=0 then 26 else if kind=1 then 138 else if kind=2 then 75 else 34

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

theorem checked14 : (List.range 16).all (fun j => decide (Valid (224+j))) = true := by decide +kernel
#print axioms checked14

theorem piece14 {i : ℕ} (hlo : 224 ≤ i) (hhi : i < 240) : Valid i := by
  have hm : i-224 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked14 (i-224) hm)
  have he : 224+(i-224) = i := by omega
  simpa only [he] using hc
#print axioms piece14

theorem checked15 : (List.range 9).all (fun j => decide (Valid (240+j))) = true := by decide +kernel
#print axioms checked15

theorem piece15 {i : ℕ} (hlo : 240 ≤ i) (hhi : i < 249) : Valid i := by
  have hm : i-240 ∈ List.range 9 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked15 (i-240) hm)
  have he : 240+(i-240) = i := by omega
  simpa only [he] using hc
#print axioms piece15

theorem valid {i : ℕ} (hi : i < 249) : Valid i := by
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
  by_cases h14 : i < 240
  · exact piece14 (by omega) h14
  exact piece15 (by omega) hi

theorem old_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 26)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (oldContract i).lower ≤ S.card) (hdefect : (oldContract i).defect ≤ Defect S) :
    (oldContract i).target ≤ (Pool S).card := by
  interval_cases i
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 122)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData158375.query 2)
      (SourceQueryData158375.conditions (by decide)) (RowSources158375.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 22) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 100) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 151) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 29) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 55) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 35) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 223) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 157) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 16) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 201) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 25) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 23)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas109474.actual_source (i := 26) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 125) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 139) (by decide)
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 136)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 224) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 219) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 220) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 221) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 222) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 225) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 226) (by decide)
      hN hground hS hsize hdefect
  · exact SourceAtlas94488.actual_source (i := 227) (by decide)
      hN hground hS hsize hdefect

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 249)
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
  · have hiq : (provider i).index < 138 := by simpa [capacity, h1] using hv.2.1
    have hb := CorrelatedSource118533.actual_plan_source (SourceQueryData88404.query (provider i).index)
      (SourceQueryData88404.conditions (by omega : (provider i).index < 172))
      (SourceQueryFloors88404.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, ofPlan] using hl)
      (by simpa [reference, h0, h1, ofPlan] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, ofPlan] using hb)
  by_cases h2 : (provider i).kind=2
  · have hiq : (provider i).index < 75 := by simpa [capacity, h2] using hv.2.1
    have hb := RunSource109474.actual_run_plan_source (RunPlans88404.plan (provider i).index)
      (RunFacts88404.conditions hiq) (SourceRunFloors88404.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, h2, ofRun] using hl)
      (by simpa [reference, h0, h1, h2, ofRun] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, h2, ofRun] using hb)
  have hiq : (provider i).index < 34 := by simpa [capacity, h0, h1, h2] using hv.2.1
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
end JSP233.SourceAtlas88404
