module

public import Erdos272.Certificates.ForcedDual209
public import Erdos272.Arithmetic.DualFrontier209
public import Erdos272.Arithmetic.FactorFullCertificate209
public import Erdos272.Arithmetic.SplitChecks209
public import Erdos272.Arithmetic.FullPrefix209_038

@[expose] public section
namespace JSP233.FullPrefix209_039
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 1000000
private theorem checked_small_1277952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1277952 1024 776901735500523078 496421614345 777524382330845640 497217646053 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1278976 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1278976 1024 777524382330845640 497217646053 778146925760340436 498014183127 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1280000 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1280000 1024 778146925760340436 498014183127 778769415144212024 498811288479 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1281024 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1281024 1024 778769415144212024 498811288479 779391825282543081 499608929639 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1282048 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1282048 1024 779391825282543081 499608929639 780014642632528769 500407730513 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1283072 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1283072 1024 780014642632528769 500407730513 780636825699548645 501206354979 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1284096 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1284096 1024 780636825699548645 501206354979 781259380855233296 502006094403 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1285120 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1285120 1024 781259380855233296 502006094403 781882162835530919 502806763091 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1277952 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1277952 8192 776901735500523078 496421614345 781882162835530919 502806763091 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1277952 776901735500523078 496421614345 777524382330845640 497217646053 7168 781882162835530919 502806763091 checked_small_1277952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1278976 777524382330845640 497217646053 778146925760340436 498014183127 6144 781882162835530919 502806763091 checked_small_1278976 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1280000 778146925760340436 498014183127 778769415144212024 498811288479 5120 781882162835530919 502806763091 checked_small_1280000 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1281024 778769415144212024 498811288479 779391825282543081 499608929639 4096 781882162835530919 502806763091 checked_small_1281024 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1282048 779391825282543081 499608929639 780014642632528769 500407730513 3072 781882162835530919 502806763091 checked_small_1282048 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1283072 780014642632528769 500407730513 780636825699548645 501206354979 2048 781882162835530919 502806763091 checked_small_1283072 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1284096 780636825699548645 501206354979 781259380855233296 502006094403 1024 781882162835530919 502806763091 checked_small_1284096 checked_small_1285120)))))))
#print axioms checked_part_1277952
private theorem checked_small_1286144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1286144 1024 781882162835530919 502806763091 782504448576155143 503607431031 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1287168 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1287168 1024 782504448576155143 503607431031 783126963838545369 504409031623 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1288192 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1288192 1024 783126963838545369 504409031623 783749623132752605 505211455351 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1289216 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1289216 1024 783749623132752605 505211455351 784371934098896518 506014067401 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1290240 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1290240 1024 784371934098896518 506014067401 784994599062376164 506817773593 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1291264 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1291264 1024 784994599062376164 506817773593 785617275940229995 507622132947 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1292288 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1292288 1024 785617275940229995 507622132947 786239595055324117 508426667385 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1293312 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1293312 1024 786239595055324117 508426667385 786862082806176852 509232057145 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1286144 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1286144 8192 781882162835530919 502806763091 786862082806176852 509232057145 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1286144 781882162835530919 502806763091 782504448576155143 503607431031 7168 786862082806176852 509232057145 checked_small_1286144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1287168 782504448576155143 503607431031 783126963838545369 504409031623 6144 786862082806176852 509232057145 checked_small_1287168 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1288192 783126963838545369 504409031623 783749623132752605 505211455351 5120 786862082806176852 509232057145 checked_small_1288192 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1289216 783749623132752605 505211455351 784371934098896518 506014067401 4096 786862082806176852 509232057145 checked_small_1289216 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1290240 784371934098896518 506014067401 784994599062376164 506817773593 3072 786862082806176852 509232057145 checked_small_1290240 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1291264 784994599062376164 506817773593 785617275940229995 507622132947 2048 786862082806176852 509232057145 checked_small_1291264 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1292288 785617275940229995 507622132947 786239595055324117 508426667385 1024 786862082806176852 509232057145 checked_small_1292288 checked_small_1293312)))))))
#print axioms checked_part_1286144
private theorem checked_small_1294336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1294336 1024 786862082806176852 509232057145 787484730432106983 510038291399 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1295360 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1295360 1024 787484730432106983 510038291399 788107224756712779 510844964637 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1296384 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1296384 1024 788107224756712779 510844964637 788729600942538436 511652122013 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1297408 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1297408 1024 788729600942538436 511652122013 789352327002308225 512460370841 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1298432 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1298432 1024 789352327002308225 512460370841 789974650950669824 513268735039 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1299456 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1299456 1024 789974650950669824 513268735039 790597237081180283 514078077255 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1300480 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1300480 1024 790597237081180283 514078077255 791219835200323133 514888072675 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1301504 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1301504 1024 791219835200323133 514888072675 791842236793966215 515698449733 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1294336 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1294336 8192 786862082806176852 509232057145 791842236793966215 515698449733 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1294336 786862082806176852 509232057145 787484730432106983 510038291399 7168 791842236793966215 515698449733 checked_small_1294336 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1295360 787484730432106983 510038291399 788107224756712779 510844964637 6144 791842236793966215 515698449733 checked_small_1295360 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1296384 788107224756712779 510844964637 788729600942538436 511652122013 5120 791842236793966215 515698449733 checked_small_1296384 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1297408 788729600942538436 511652122013 789352327002308225 512460370841 4096 791842236793966215 515698449733 checked_small_1297408 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1298432 789352327002308225 512460370841 789974650950669824 513268735039 3072 791842236793966215 515698449733 checked_small_1298432 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1299456 789974650950669824 513268735039 790597237081180283 514078077255 2048 791842236793966215 515698449733 checked_small_1299456 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1300480 790597237081180283 514078077255 791219835200323133 514888072675 1024 791842236793966215 515698449733 checked_small_1300480 checked_small_1301504)))))))
#print axioms checked_part_1294336
private theorem checked_small_1302528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1302528 1024 791842236793966215 515698449733 792464745414508210 516509603529 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1303552 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1303552 1024 792464745414508210 516509603529 793087332691790899 517321497377 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1304576 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1304576 1024 793087332691790899 517321497377 793709849490033163 518133936813 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1305600 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1305600 1024 793709849490033163 518133936813 794332349559128837 518946991847 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1306624 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1306624 1024 794332349559128837 518946991847 794954981191416966 519760856335 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1307648 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1307648 1024 794954981191416966 519760856335 795577234639589051 520574863601 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1308672 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1308672 1024 795577234639589051 520574863601 796199753083894797 521389854853 = true := by
  apply ForcedDual209.checked
  decide +kernel

private theorem checked_small_1309696 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1309696 1024 796199753083894797 521389854853 796822517763135821 522205806305 = true := by
  apply ForcedDual209.checked
  decide +kernel

theorem checked_part_1302528 : DualFrontier209.checkFrom FactorFullCertificate209.phi 1302528 8192 791842236793966215 515698449733 796822517763135821 522205806305 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1302528 791842236793966215 515698449733 792464745414508210 516509603529 7168 796822517763135821 522205806305 checked_small_1302528 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1303552 792464745414508210 516509603529 793087332691790899 517321497377 6144 796822517763135821 522205806305 checked_small_1303552 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1304576 793087332691790899 517321497377 793709849490033163 518133936813 5120 796822517763135821 522205806305 checked_small_1304576 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1305600 793709849490033163 518133936813 794332349559128837 518946991847 4096 796822517763135821 522205806305 checked_small_1305600 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1306624 794332349559128837 518946991847 794954981191416966 519760856335 3072 796822517763135821 522205806305 checked_small_1306624 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1307648 794954981191416966 519760856335 795577234639589051 520574863601 2048 796822517763135821 522205806305 checked_small_1307648 (SplitChecks209.frontier_join FactorFullCertificate209.phi 1024 1308672 795577234639589051 520574863601 796199753083894797 521389854853 1024 796822517763135821 522205806305 checked_small_1308672 checked_small_1309696)))))))
#print axioms checked_part_1302528
theorem checked : DualFrontier209.checkFrom FactorFullCertificate209.phi 1277952 32768 776901735500523078 496421614345 796822517763135821 522205806305 = true := by
  exact (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1277952 776901735500523078 496421614345 781882162835530919 502806763091 24576 796822517763135821 522205806305 checked_part_1277952 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1286144 781882162835530919 502806763091 786862082806176852 509232057145 16384 796822517763135821 522205806305 checked_part_1286144 (SplitChecks209.frontier_join FactorFullCertificate209.phi 8192 1294336 786862082806176852 509232057145 791842236793966215 515698449733 8192 796822517763135821 522205806305 checked_part_1294336 checked_part_1302528)))
theorem block_sound :
    (796822517763135821 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1310720 ∧
     522205806305 = FrontierCheck209.triangle FactorFullCertificate209.phi 1310720) ∧
    ∀ t, 1277952 < t → t ≤ 1310720 → DualFrontier209.Good t
      (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
      (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  exact DualFrontier209.checkFrom_sound FactorFullCertificate209.phi 32768 1277952 776901735500523078 496421614345 796822517763135821 522205806305 FullPrefix209_038.endpoint.1 FullPrefix209_038.endpoint.2 checked
theorem endpoint :
    796822517763135821 = FrontierCheck209.massFloor FactorFullCertificate209.phi 1310720 ∧
    522205806305 = FrontierCheck209.triangle FactorFullCertificate209.phi 1310720 := block_sound.1
theorem good (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 1310720) : DualFrontier209.Good t
    (FrontierCheck209.massFloor FactorFullCertificate209.phi t)
    (FrontierCheck209.triangle FactorFullCertificate209.phi t) := by
  by_cases hprev : t ≤ 1277952
  · exact FullPrefix209_038.good t ht hprev
  · exact block_sound.2 t (by omega) htN
#print axioms checked
#print axioms good
end JSP233.FullPrefix209_039
